module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSU3
public import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Q : Type} [Group Q]

theorem mem_of_commute_elemAbelian_nine (hQ : Vol2Native.SQTKHypCat Q) {E : Subgroup Q}
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {x : Q} (hx3 : x ^ 3 = 1)
    (hxc : ∀ e ∈ E, x * e = e * x) : x ∈ E := by
  have := hQ.finite
  by_contra hxE
  have hx1 : x ≠ 1 := fun h1 => hxE (h1 ▸ one_mem E)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcomm : ∀ (a : ↥E) (b : ↥(Subgroup.zpowers x)),
      Commute (E.subtype a) ((Subgroup.zpowers x).subtype b) := by
    intro a b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : Q) (b : Q)
    rw [← hn]
    exact Commute.zpow_right (hxc a a.2).symm n
  let f : ↥E × ↥(Subgroup.zpowers x) →* Q :=
    MonoidHom.noncommCoprod E.subtype (Subgroup.zpowers x).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : Q) * b = 1 := hab
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hbE : (b : Q) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hab']
      exact inv_mem a.2
    have hb1 : (b : Q) = 1 := by
      by_contra hb1
      apply hxE
      have h3n : ¬ (3 : ℤ) ∣ n := by
        intro hd
        obtain ⟨m, rfl⟩ := hd
        apply hb1
        rw [← hn, zpow_mul, show (x ^ (3 : ℤ)) = x ^ 3 from zpow_natCast x 3, hx3, one_zpow]
      have hsq : x = (x ^ n) ^ n := by
        rw [← zpow_mul, ← zpow_mod_orderOf, hox]
        conv_lhs => rw [← zpow_one x]
        congr 1
        push_cast
        have h1 : n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases h1 with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
      rw [hsq]
      exact zpow_mem (hn ▸ hbE) n
    have ha1 : (a : Q) = 1 := by rw [hb1, mul_one] at hab'; exact hab'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcard : Nat.card (↥E × ↥(Subgroup.zpowers x)) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_zpowers, hox, hE9]
    norm_num
  have hA := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (A := ↥E × ↥(Subgroup.zpowers x))
    (fun a b => Prod.ext (hE.1.is_comm.comm a.1 b.1)
      (Subtype.ext (by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
        change (a.2 : Q) * b.2 = b.2 * a.2
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm])))
    (fun a => Prod.ext (Subtype.ext (by
        change ((a.1 : Q)) ^ 3 = 1
        exact hE.2 _ a.1.2))
      (Subtype.ext (by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        change ((a.2 : Q)) ^ 3 = 1
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow])))
    hcard f hf (H := ⊤) le_top
  have h2 := hQ.sqt 3 Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

theorem map_perfectResidual_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    (CFSG.perfectResidual G).map (φ : G →* H) = CFSG.perfectResidual H := by
  rw [CFSG.perfectResidual, CFSG.perfectResidual, Subgroup.map_iInf _ φ.injective]
  exact iInf_congr fun n => map_derivedSeries_eq φ.surjective n

theorem not_mem_center_sl2 {F : Type} [Field F] {c : Matrix.SpecialLinearGroup (Fin 2) F}
    (hc : orderOf c = 3) : c ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro h1
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  rw [Fintype.card_fin] at hr
  have h2 : c ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hc] at this
  norm_num at this

variable {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.false_of_residual_sl2 (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    (eR : ↥(CFSG.perfectResidual ↥(K ⊓ Subgroup.centralizer ({v} : Set Q))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) : False := by
  classical
  have := hQ.finite
  set C := K ⊓ Subgroup.centralizer ({v} : Set Q) with hCdef
  set R := CFSG.perfectResidual ↥C with hRdef
  let ι : ↥R →* Q := C.subtype.comp R.subtype
  have hι : Function.Injective ι := C.subtype_injective.comp R.subtype_injective
  have hιv : ∀ r : ↥R, ι r ∈ Subgroup.centralizer ({v} : Set Q) := fun r => (r : ↥C).2.2
  have hconjC : ∀ l ∈ L, ∀ x ∈ C, l * x * l⁻¹ ∈ C := by
    intro l hl x hx
    have hlv : Commute l v := (h.L_cent l hl).symm
    have hxv : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    exact ⟨(Subgroup.mem_normalizer_iff.mp (h.L_norm hl) x).mp hx.1,
      Subgroup.mem_centralizer_singleton_iff.mpr ((hlv.mul_left hxv).mul_left hlv.inv_left)⟩
  let φ : ∀ l ∈ L, ↥C ≃* ↥C := fun l hl =>
    { toFun := fun x => ⟨l * x * l⁻¹, hconjC l hl x x.2⟩
      invFun := fun x => ⟨l⁻¹ * x * l, by simpa using hconjC l⁻¹ (inv_mem hl) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hRchar : ∀ ψ : ↥C ≃* ↥C, R.map (ψ : ↥C →* ↥C) = R := fun ψ =>
    Subgroup.characteristic_iff_map_eq.mp inferInstance ψ
  have hN : (L.comap ι).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (h.L_star (hιv g)) (ι n)).mp hn⟩
  have hq := CFSG.QuasithinUnique.Ch1.isQuasisimple_sl2 (F := F) (by rw [hF]; norm_num)
  have hRq : CFSG.IsQuasisimple ↥R :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eR).2 hq
  have hRc : Nat.card R = 120 := by
    rw [Nat.card_congr eR.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    norm_num
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      ⟨Group.isPerfect_def.mp hRq.1, hRq.2.1⟩ (L.comap ι) with hcen | htop
  ·
    have hcentral : ∀ l ∈ L, ∀ r : ↥R, l * ι r = ι r * l := by
      intro l hl
      let α : MulAut ↥R :=
        ((φ l hl).subgroupMap R).trans (MulEquiv.subgroupCongr (hRchar (φ l hl)))
      have hα : ∀ r : ↥R, ι (α r) = l * ι r * l⁻¹ := fun r => rfl
      have hα1 : α = 1 := eq_one_of_inv_mul_mem_center hRq.1 fun r => hcen (by
        rw [Subgroup.mem_comap, map_mul, map_inv, hα]
        have h1 : (ι r)⁻¹ * l⁻¹ * (ι r)⁻¹⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (h.L_star (inv_mem (hιv r))) l⁻¹).mp (inv_mem hl)
        have h2 : (l * ι r * l⁻¹)⁻¹ * ι r = l * ((ι r)⁻¹ * l⁻¹ * (ι r)⁻¹⁻¹) := by group
        rw [h2]
        exact mul_mem hl h1)
      intro r
      have h1 : ι (α r) = ι r := by rw [hα1]; rfl
      rw [hα] at h1
      calc l * ι r = l * ι r * l⁻¹ * l := by group
        _ = ι r * l := by rw [h1]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 3 (by rw [hRc]; norm_num)
    have hc3 : ι c ^ 3 = 1 := by
      rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    have hcP : ι c ∈ P := mem_of_commute_elemAbelian_nine hQ h.P_elem h.P_card hc3
      fun p hp => (hcentral p (h.P_le hp) c).symm
    apply not_mem_center_sl2 (F := F) (c := eR c) (by rw [MulEquiv.orderOf_eq, hc])
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨r, rfl⟩ := eR.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact hι (by rw [map_mul, map_mul]; exact (hcentral _ (h.P_le hcP) r).symm)
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 5 (by rw [hRc]; norm_num)
    have huL : ι u ∈ L := by
      have : u ∈ L.comap ι := by rw [htop]; trivial
      exact this
    have huo : orderOf (ι u) = 5 := by rw [orderOf_injective ι hι, hu]
    have h3 := h.L_three _ huL (by rw [huo]; decide)
    have := orderOf_dvd_of_pow_eq_one h3
    rw [huo] at this
    norm_num at this

theorem Conf12626.false_of_conj_residual (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {X : Type} [Group X] (e : ↥K ≃* X) {t : X}
    (ht : ∀ k : ↥K, e (h.nu k) = t * e k * t⁻¹) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 5)
    (eR : ↥(CFSG.perfectResidual ↥(Subgroup.centralizer ({t} : Set X))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) : False := by
  have hfix : ∀ k : ↥K, h.nu k = k ↔ (k : Q) * v = v * k := by
    intro k
    constructor
    · intro h1
      have h2 := congrArg Subtype.val h1
      rw [h.coe_nu_apply] at h2
      calc (k : Q) * v = v * k * v⁻¹ * v := by rw [h2]
        _ = v * k := by group
    · intro h1
      apply Subtype.ext
      rw [h.coe_nu_apply, ← h1, mul_inv_cancel_right]
  have hfix' : ∀ k : ↥K, h.nu k = k ↔ e k * t = t * e k := by
    intro k
    rw [← e.injective.eq_iff, ht]
    constructor
    · intro h1
      calc e k * t = t * e k * t⁻¹ * t := by rw [h1]
        _ = t * e k := by group
    · intro h1
      rw [← h1, mul_inv_cancel_right]
  let eC : ↥(K ⊓ Subgroup.centralizer ({v} : Set Q)) ≃*
      ↥(Subgroup.centralizer ({t} : Set X)) :=
    { toFun := fun x => ⟨e ⟨x, x.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        ((hfix' _).mp ((hfix _).mpr (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)))⟩
      invFun := fun y => ⟨e.symm y, (e.symm y).2, Subgroup.mem_centralizer_singleton_iff.mpr
        ((hfix _).mp ((hfix' _).mpr (by
          rw [MulEquiv.apply_symm_apply]
          exact Subgroup.mem_centralizer_singleton_iff.mp y.2)))⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change e (⟨x, x.2.1⟩ * ⟨y, y.2.1⟩) = e ⟨x, x.2.1⟩ * e ⟨y, y.2.1⟩
        rw [map_mul]) }
  exact h.false_of_residual_sl2 hQ hF (((eC.subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_perfectResidual_mulEquiv eC))).trans eR)

end CFSG.Quasithin.H13.S126C
