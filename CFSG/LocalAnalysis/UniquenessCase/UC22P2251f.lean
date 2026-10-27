module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
import CFSG.Quasithin.EmptyFaithful.S146zXGIdent
import CFSG.Monster.Existence.StdOdd.Coprime
import CFSG.RankThree.PartOne.S11c.Simple168

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext (IsInternalDirect)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x (natI natC natIi)

namespace P2251f

open Equiv

section Aut

theorem dvd_of_dvd_mul_24 {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 24 * r) : p ∣ r := by
  refine ((Nat.Prime.dvd_mul hp).1 h).resolve_left fun h24 => ?_
  rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 ^ 3 * 3 from h24) with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

theorem card_perm_fin_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_card_eq_two_pow {Y : Type} [Group Y] [Finite Y] {Q : Subgroup Y} (hQ2 : IsPGroup 2 Q)
    (hQ : Q ≠ ⊥) {r : ℕ} (hr : Odd r) (hY : Nat.card Y ∣ 8 * r) :
    ∃ n, 1 ≤ n ∧ n ≤ 3 ∧ Nat.card Q = 2 ^ n := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
  have h1 : 2 ^ n ∣ 2 ^ 3 * r := by
    rw [← hn, show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact (Subgroup.card_subgroup_dvd_card Q).trans hY
  have h2 : 2 ^ n ∣ 2 ^ 3 :=
    (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hr)).dvd_of_dvd_mul_right h1
  refine ⟨n, Nat.one_le_iff_ne_zero.2 fun h0 => hQ ?_, (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2, hn⟩
  rw [← Subgroup.card_eq_one, hn, h0, pow_zero]

theorem exists_commute_of_card {W : Type} [Group W] [Finite W] {p : ℕ} [Fact p.Prime] {g : W}
    (hg : orderOf g = p) {R : Subgroup W} (hgR : ∀ s ∈ R, g * s * g⁻¹ ∈ R) (hR2 : IsPGroup 2 R)
    (hR : ¬ Nat.card R ≡ 1 [MOD p]) : ∃ t ∈ R, orderOf t = 2 ∧ g * t = t * g := by
  have hcnt := CFSG.Monster.Existence.StdOdd.card_modEq_inf_centralizer (p := p) (P := zpowers g) (F := R)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one]))
    (zpowers_le.2 (CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem hgR))
  have hC : IsPGroup 2 ↥(R ⊓ centralizer (zpowers g : Set W)) := hR2.to_le inf_le_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hC
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hn, pow_zero] at hcnt
    exact hR hcnt
  obtain ⟨⟨t, htm⟩, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ centralizer (zpowers g : Set W))) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨t, (Subgroup.mem_inf.1 htm).1, by rwa [Subgroup.orderOf_mk] at ht,
    mem_centralizer_iff.1 (Subgroup.mem_inf.1 htm).2 g (mem_zpowers g)⟩

theorem nonempty_mulEquiv_alt_five {X : Type} [Group X] (h : IsL2Ev X 2) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI := Fintype.ofFinite F
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 2 2 two_ne_zero]
  obtain ⟨e₂⟩ := CFSG.Quasithin.S146zX.nonempty_mulEquiv_sl_two_four_of_alt_five
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans
    ((CFSG.GorensteinWalter.FieldTransport.specialLinearGroupMulEquiv
      (FiniteField.ringEquivOfCardEq hcard)).trans e₂)⟩

theorem false_of_five {Y Z : Type} [Group Y] [Finite Y] [Group Z] (e : Y ≃* Z) {j : Z →* Perm (Fin 5)}
    (hj : Function.Injective j) {φ : Perm (Fin 5) →* MulAut Z} (hφ : Function.Bijective φ)
    (hφj : ∀ c z, j (φ c z) = c * j z * c⁻¹) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {σ : MulAut Y}
    (hσ : orderOf σ = p) {Q : Subgroup Y} (hQ2 : IsPGroup 2 Q) (hQ : Q ≠ ⊥) (hσQ : ∀ q ∈ Q, σ q ∈ Q) :
    False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hφ.2 (MulAut.congr e σ)
  have hco : orderOf c = p := by rw [← orderOf_injective φ hφ.1 c, hc, MulEquiv.orderOf_eq, hσ]
  have h5 : p ∣ 24 * 5 := by
    rw [← hco]
    exact (orderOf_dvd_natCard c).trans (dvd_of_eq (card_perm_fin_five.trans (by norm_num)))
  obtain rfl : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (dvd_of_dvd_mul_24 hp hp5 h5)
  set ι : Y →* Perm (Fin 5) := j.comp e.toMonoidHom
  have hιi : Function.Injective ι := hj.comp e.injective
  have hσc : ∀ y, ι (σ y) = c * ι y * c⁻¹ := fun y => by
    have h1 := hφj c (e y)
    rwa [hc, show MulAut.congr e σ (e y) = e (σ y) by
      show e (σ (e.symm (e y))) = e (σ y); rw [MulEquiv.symm_apply_apply]] at h1
  obtain ⟨n, hn1, hn3, hn⟩ := exists_card_eq_two_pow hQ2 hQ (r := 15) ⟨7, by norm_num⟩
    ((Subgroup.card_dvd_of_injective ι hιi).trans (dvd_of_eq (card_perm_fin_five.trans (by norm_num))))
  obtain ⟨t, -, ht, hct⟩ := exists_commute_of_card hco (R := Q.map ι)
    (by rintro _ ⟨q, hq, rfl⟩; exact ⟨σ q, hσQ q hq, hσc q⟩) (hQ2.map ι)
    (by rw [Subgroup.card_map_of_injective hιi, hn]; interval_cases n <;> decide)
  have h10 : orderOf (c * t) = 5 * 2 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (show Commute c t from hct) (by rw [hco, ht]; decide),
      hco, ht]
  have h10' := pow_orderOf_eq_one (c * t)
  rw [h10] at h10'
  rcases CFSG.SeitzReduction.RankOne.perm_five_pow_ten (c * t) h10' with h | h <;>
    (have := orderOf_dvd_of_pow_eq_one h; rw [h10] at this; norm_num at this)

theorem false_of_isL3 {Y : Type} [Group Y] [Finite Y] (h : IsL3 Y 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {σ : MulAut Y} (hσ : orderOf σ = p) {Q : Subgroup Y} (hQ2 : IsPGroup 2 Q) (hQ : Q ≠ ⊥)
    (hσQ : ∀ q ∈ Q, σ q ∈ Q) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup Y := PartTwo.isSimpleGroup_of_isL3 h
  have h168 : Nat.card Y = 168 := PartTwo.card_eq_of_isL3 h
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    refine (injective_iff_map_eq_one _).2 fun g hg => ?_
    have hgc : g ∈ center Y := mem_center_iff.2 fun z =>
      (mul_inv_eq_iff_eq_mul.1 (show g * z * g⁻¹ = z from DFunLike.congr_fun hg z)).symm
    rwa [PartTwo.center_eq_bot_of_isL3 h, mem_bot] at hgc
  have hidx : (MulAut.conj : Y →* MulAut Y).range.index = 2 := by
    have h1 := (MulAut.conj : Y →* MulAut Y).range.card_mul_index
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, h168,
      CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two h] at h1
    omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  have hσσ : σ = (σ * σ) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, ← hσ, pow_orderOf_eq_one, one_mul]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (show σ ∈ (MulAut.conj : Y →* MulAut Y).range by
    rw [hσσ]
    exact pow_mem (mul_self_mem_of_index_two hidx σ) _)
  have hgo : orderOf g = p := by rw [← orderOf_injective _ hinj g, hg, hσ]
  have h7 : p ∣ 24 * 7 := by
    rw [← hgo]
    exact (orderOf_dvd_natCard g).trans (dvd_of_eq (h168.trans (by norm_num)))
  obtain rfl : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (dvd_of_dvd_mul_24 hp hp5 h7)
  have hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun q hq => by
    rw [← MulAut.conj_apply, hg]
    exact hσQ q hq
  obtain ⟨n, hn1, hn3, hn⟩ := exists_card_eq_two_pow hQ2 hQ (r := 21) ⟨10, by norm_num⟩
    (dvd_of_eq (h168.trans (by norm_num)))
  rcases (show n ≤ 2 ∨ n = 3 by omega) with hn2 | rfl
  · obtain ⟨t, -, ht, hgt⟩ := exists_commute_of_card hgo hgQ hQ2 (by rw [hn]; interval_cases n <;> decide)
    have htz : t ∈ zpowers g := by
      rw [← PartTwo.centralizer_eq_of_isL3_seven h (by rw [Nat.card_zpowers, hgo] : Nat.card (zpowers g) = 7),
        mem_centralizer_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 (SetLike.mem_coe.1 hy)
      exact ((show Commute g t from hgt).zpow_left j).eq
    have := orderOf_dvd_of_mem_zpowers htz
    rw [ht, hgo] at this
    norm_num at this
  · exact CFSG.RankThree.PartOne.simple168_no_normalized_two_subgroup h168 Q hQ2 (le_of_eq hn.symm) g hgo hgQ

theorem eq_one_of_normalizes {Y : Type} [Group Y] [Finite Y] (hY : IsL2Ev Y 2 ∨ IsL3 Y 1 ∨ IsS5 Y) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {σ : MulAut Y} {k : ℕ} (hσ : σ ^ p ^ k = 1) {Q : Subgroup Y}
    (hQ2 : IsPGroup 2 Q) (hQ : Q ≠ ⊥) (hσQ : ∀ q ∈ Q, σ q ∈ Q) : σ = 1 := by
  by_contra hσ1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hσ)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hσ1 (orderOf_eq_one_iff.1 (by rw [hj, pow_zero]))
  have hτ : orderOf (σ ^ (orderOf σ / p)) = p :=
    orderOf_pow_orderOf_div (by rw [hj]; exact pow_ne_zero _ hp.ne_zero) (by rw [hj]; exact dvd_pow_self p hj0)
  have hpow : ∀ (n : ℕ), ∀ q ∈ Q, (σ ^ n) q ∈ Q := by
    intro n
    induction n with
    | zero => intro q hq; rwa [pow_zero, MulAut.one_apply]
    | succ n ih => intro q hq; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hσQ q hq)
  rcases hY with h | h | h
  · obtain ⟨e⟩ := nonempty_mulEquiv_alt_five h
    exact false_of_five e (j := (alternatingGroup (Fin 5)).subtype) (alternatingGroup (Fin 5)).subtype_injective
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num) (by norm_num))
      (fun c z => MulAut.conjNormal_apply c z) hp hp5 hτ hQ2 hQ (hpow _)
  · exact false_of_isL3 h hp hp5 hτ hQ2 hQ (hpow _)
  · obtain ⟨e⟩ : Nonempty (Y ≃* Perm (Fin 5)) := h
    exact false_of_five e (j := MonoidHom.id _) (fun _ _ h => h) CFSG.Monster.B.TwoA.sym5_conj_bijective
      (fun c z => MulAut.conj_apply c z) hp hp5 hτ hQ2 hQ (hpow _)

theorem commute_of_bad {X : Type} [Group X] [Finite X] {N Q : Subgroup X}
    (hN : IsL2Ev ↥N 2 ∨ IsL3 ↥N 1 ∨ IsS5 ↥N) (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q) (hQ : Q ≠ ⊥) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {g : X} {k : ℕ} (hgk : g ^ p ^ k = 1) (hgN : g ∈ normalizer (N : Set X))
    (hgQ : g ∈ normalizer (Q : Set X)) : ∀ y ∈ N, g * y = y * g := by
  have hσ := eq_one_of_normalizes hN hp hp5 (σ := N.normalizerMonoidHom ⟨g, hgN⟩) (k := k)
    (by rw [← map_pow, show (⟨g, hgN⟩ : normalizer (N : Set X)) ^ p ^ k = 1 from
      Subtype.ext (by simpa using hgk), map_one]) hQ2.comap_subtype
    (fun h => hQ ((subgroupOf_eq_bot.1 h).eq_bot_of_le hQN))
    (fun q hq => mem_subgroupOf.2 ((mem_normalizer_iff.1 hgQ q).1 (mem_subgroupOf.1 hq)))
  intro y hy
  exact mul_inv_eq_iff_eq_mul.1 (congrArg Subtype.val (DFunLike.congr_fun hσ (⟨y, hy⟩ : ↥N)) : g * y * g⁻¹ = y)

theorem ne_bot_of_bad {X : Type} [Group X] [Finite X] {H : Subgroup X}
    (h : IsL2Ev ↥H 2 ∨ IsL3 ↥H 1 ∨ IsS5 ↥H) : H ≠ ⊥ := by
  rintro rfl
  have h1 : Nat.card (⊥ : Subgroup X) = 1 := Subgroup.card_bot
  rcases h with h | h | h
  · rw [P22x.card_of_isL2Ev h] at h1
    norm_num at h1
  · rw [PartTwo.card_eq_of_isL3 h] at h1
    norm_num at h1
  · obtain ⟨e⟩ : Nonempty (↥(⊥ : Subgroup X) ≃* Perm (Fin 5)) := h
    rw [Nat.card_congr e.toEquiv, card_perm_fin_five] at h1
    norm_num at h1

end Aut

section Conj

variable {X : Type} [Group X] {m : ℕ} {H : Subgroup X} {Nb : Fin m → Subgroup X}

theorem commOn_map {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) X V}
    {A A' : Subgroup X} {U U' : Submodule (ZMod 2) V} {g : X} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A')
    (hgU : ∀ u ∈ U, ρ g u ∈ U') : ∀ w ∈ commOn ρ A U, ρ g w ∈ commOn ρ A' U' := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hw
    have h1 : ρ g (ρ a u - u) = ρ (g * a * g⁻¹) (ρ g u) - ρ g u := by
      rw [map_sub, show ρ (g * a * g⁻¹) (ρ g u) = ρ g (ρ a u) from ?_]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        show ρ g⁻¹ (ρ g u) = u from ?_]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h1]
    exact P22x.sub_mem_commOn (hgA a ha) (hgU u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem piMul_conj (hd : IsInternalDirect H Nb) {g : X} (hg : ∀ k, g ∈ normalizer (Nb k : Set X))
    (f : ∀ k, ↥(Nb k)) :
    P22y.piMul hd (fun k => ⟨g * (f k : X) * g⁻¹, (mem_normalizer_iff.1 (hg k) _).1 (f k).2⟩) =
      g * P22y.piMul hd f * g⁻¹ := by
  rw [P22y.piMul, Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply, ← MulAut.conj_apply]
  exact (Finset.map_noncommProd Finset.univ (fun k => (f k : X)) _ (MulAut.conj g)).symm

theorem mem_normalizer_proj [Finite X] (hd : IsInternalDirect H Nb) {g : X}
    (hg : ∀ k, g ∈ normalizer (Nb k : Set X)) {A : Subgroup X} (hgA : g ∈ normalizer (A : Set X)) (j : Fin m) :
    g ∈ normalizer (P2251e.proj hd j A : Set X) := by
  refine CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem fun b hb => ?_
  obtain ⟨f, hfA, rfl⟩ := (P2251e.mem_proj hd j).1 hb
  refine (P2251e.mem_proj hd j).2
    ⟨fun k => ⟨g * (f k : X) * g⁻¹, (mem_normalizer_iff.1 (hg k) _).1 (f k).2⟩, ?_, rfl⟩
  rw [piMul_conj hd hg f]
  exact (mem_normalizer_iff.1 hgA _).1 hfA

end Conj

theorem isPGroup_zpowers_of_pow {X : Type} [Group X] {p : ℕ} [hp : Fact p.Prime] {y : X} {n : ℕ}
    (h : y ^ p ^ n = 1) : IsPGroup p (zpowers y) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem mem_normalizer_mbarImage {G : Type} [Group G] [Finite G] {M V Y : Subgroup G} {x : G} (hxM : x ∈ M)
    (hxY : x ∈ normalizer (Y : Set G)) :
    (QuotientGroup.mk ⟨x, hxM⟩ : MBar M V) ∈ normalizer (mbarImage M V Y : Set (MBar M V)) := by
  have h1 : (⟨x, hxM⟩ : ↥M) ∈ normalizer ((Y.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    rw [mem_normalizer_iff]
    intro h
    exact mem_normalizer_iff.1 hxY (h : G)
  exact le_normalizer_map (QuotientGroup.mk' (kerAct M V).normalCore) (mem_map_of_mem _ h1)

end P2251f

open P2251f

theorem uc22p2251f_mem_centralizer {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G)
    (h3 : S22_3_3 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hS3 : ∀ k, k ≠ i → IsL2Ev ↥(Nb k) 1)
    (hbad : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {x : G}
    (hxM : x ∈ D.M) (hxp : IsPGroup p (zpowers x)) (hxJ : x ∈ normalizer (jOf D.T : Set G))
    (hxE : x ∈ centralizer (proofE D : Set G)) : x ∈ centralizer (D.U : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hV := P22x.uc22p22xf_hV D
  have hd := hNb.1
  obtain ⟨n₀, hn₀⟩ := hxp ⟨x, mem_zpowers x⟩
  have hx1 : x ^ p ^ n₀ = 1 := by simpa using congrArg Subtype.val hn₀
  have hxM1 : (⟨x, hxM⟩ : ↥D.M) ^ p ^ n₀ = 1 := Subtype.ext (by simpa using hx1)
  set xb : MBar D.M D.U := QuotientGroup.mk ⟨x, hxM⟩ with hxb
  have hxb1 : xb ^ p ^ n₀ = 1 := by rw [hxb, ← QuotientGroup.mk_pow, hxM1, QuotientGroup.mk_one]
  have hxbN : xb ∈ normalizer (mbarImage D.M D.U (proofN D) : Set (MBar D.M D.U)) :=
    mem_normalizer_mbarImage hxM (uc22p22t_M_le_normalizer_jOf D hxM)
  have hxbJ : xb ∈ normalizer (mbarImage D.M D.U (jOf D.T) : Set (MBar D.M D.U)) :=
    mem_normalizer_mbarImage hxM hxJ
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ := uc22br4_exists_conjModule D.M D.U hV (P22x.uc22p22xf_hel D)
  obtain ⟨hsum, -⟩ := h3 hH c m Nb hNb Umod e ρ hc
  have hfixE : ∀ w, P22x.iota e w ∈ proofE D → ρ xb w = w := fun w hw => P22x.iota_injective e (by
    rw [hxb, P22x.iota_rho hV e ρ hc]
    exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hxE _ hw).symm)
  obtain ⟨τ, hτ⟩ := P22y.exists_perm hd (fun k => P22w.isIndecomposable_of_factorShape22 (hNb.2 k))
    (fun k => P22w.center_eq_bot_of_factorShape22 (hNb.2 k)) hxbN
  have hconj : ∀ k, ∀ a ∈ Nb k, xb * a * xb⁻¹ ∈ Nb (τ k) := fun k a ha => by
    rw [← hτ k]
    exact ⟨a, ha, rfl⟩
  have hImap : ∀ k, ∀ w ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb k),
      ρ xb w ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb (τ k)) := fun k =>
    commOn_map (hconj k) (P22x.commOn_invariant (A := mbarImage D.M D.U (proofN D)) (U := ⊤)
      (fun a ha => (mem_normalizer_iff.1 hxbN a).1 ha) fun _ _ => trivial)
  have hτj : ∀ j, j ≠ i → τ j = j := by
    intro j hj
    by_contra hne
    obtain ⟨v, hv, hvC, -, hvE⟩ := uc22p2251e_exists_fixed D Ch h3 hH c hNb e ρ hc (hS3 j hj)
    have hv' := hImap j v hv
    rw [hfixE v hvE] at hv'
    exact hvC (hsum.2 j ⟨Submodule.mem_sup_left hv,
      Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (τ j) (Submodule.mem_iSup_of_mem hne hv'))⟩)
  have hτ' : ∀ k, τ k = k := by
    intro k
    by_cases hk : k = i
    · rw [hk]
      by_contra hne
      exact hne (τ.injective (hτj (τ i) hne))
    · exact hτj k hk
  have hxbNk : ∀ k, xb ∈ normalizer (Nb k : Set (MBar D.M D.U)) := fun k =>
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem fun a ha => by
      rw [← hτ' k]
      exact hconj k a ha
  have hJM : IsPGroup 2 ↥((jOf D.T).subgroupOf D.M) :=
    (D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype
  have hcentQ : ∀ k, ∀ y ∈ P2251e.proj hd k (mbarImage D.M D.U (jOf D.T)), xb * y = y * xb := by
    intro k
    by_cases hk : k = i
    · rw [hk]
      exact fun y hy => commute_of_bad hbad (P2251e.proj_le hd i _) (P2251e.isPGroup_proj hd i (hJM.map _))
        (P2251e.proj_jOf_ne_bot D hd (ne_bot_of_bad hbad)) hp hp5 hxb1 (hxbNk i)
        (mem_normalizer_proj hd hxbNk hxbJ i) y (P2251e.proj_le hd i _ hy)
    · exact CFSG.Walter.JT.commute_of_card_le_four hp5 (isPGroup_zpowers_of_pow hxb1)
        ((P2251e.card_proj_jOf D hd (P22y.card_of_isL2Ev_one (hS3 k hk))).le.trans (by norm_num))
        (mem_normalizer_proj hd hxbNk hxbJ k)
  have hcent : ∀ a ∈ mbarImage D.M D.U (jOf D.T), xb * a = a * xb := by
    intro a ha
    obtain ⟨f, rfl⟩ := P2251e.exists_piMul hd (P22x.mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM) ha)
    have h1 : P22y.piMul hd f ∈ centralizer ({xb} : Set (MBar D.M D.U)) := by
      rw [P22y.piMul, Subgroup.noncommPiCoprod_apply]
      exact Subgroup.noncommProd_mem _ _ fun k _ =>
        mem_centralizer_singleton_iff.2 (hcentQ k _ ((P2251e.mem_proj hd k).2 ⟨f, ha, rfl⟩)).symm
    exact (mem_centralizer_singleton_iff.1 h1).symm
  have hρker : ∀ g : ↥D.M, (g : G) ∈ centralizer (D.U : Set G) → uc22br4_conjAut D.M D.U hV g = 1 :=
    fun g hg => MulEquiv.ext fun u => Subtype.ext (show (g : G) * u * (g : G)⁻¹ = u from
      mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 hg u u.2).symm)
  have hA := CFSG.Quasithin.thompson_AxB_element (D.sylowM.isPGroup.to_le (P22x.uc22p22xf_UleT D))
    (uc22br4_conjAut D.M D.U hV) (B := (jOf D.T).subgroupOf D.M) (hJM.map _) (a := ⟨x, hxM⟩)
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxM1)
      (Nat.Coprime.pow_left n₀ ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))))
    (fun b hb => by
      have h1 : (QuotientGroup.mk (⟨x, hxM⟩ * b) : MBar D.M D.U) = QuotientGroup.mk (b * ⟨x, hxM⟩) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact hcent _ (mem_map_of_mem (QuotientGroup.mk' (kerAct D.M D.U).normalCore) hb)
      have h2 : ((((⟨x, hxM⟩ * b)⁻¹ * (b * ⟨x, hxM⟩) : ↥D.M)) : G) ∈ centralizer (D.U : Set G) :=
        mem_subgroupOf.1 (normalCore_le _ (QuotientGroup.eq.1 h1))
      have h3 := hρker _ h2
      simp only [map_mul, map_inv] at h3
      exact inv_mul_eq_one.1 h3)
    (fun u hu => by
      have huJ : (u : G) ∈ centralizer (jOf D.T : Set G) := mem_centralizer_iff.2 fun y hy =>
        mul_inv_eq_iff_eq_mul.1 (congrArg Subtype.val
          (hu ⟨y, D.sylowM.le (uc22p22e_jOf_le_self D.T hy)⟩ (mem_subgroupOf.2 hy)) : y * (u : G) * y⁻¹ = u)
      exact Subtype.ext (show x * (u : G) * x⁻¹ = u from mul_inv_eq_iff_eq_mul.2
        (mem_centralizer_iff.1 hxE _ (P2251e.inf_centralizer_le_proofE D ⟨u.2, huJ⟩)).symm))
  exact mem_centralizer_iff.2 fun u hu => (mul_inv_eq_iff_eq_mul.1
    (congrArg Subtype.val (DFunLike.congr_fun hA (⟨u, hu⟩ : ↥D.U)) : x * u * x⁻¹ = u)).symm

theorem uc22p2251f_le_centralizer {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G)
    (h3 : S22_3_3 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hS3 : ∀ k, k ≠ i → IsL2Ev ↥(Nb k) 1)
    (hbad : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {P : Subgroup G} (hPM : P ≤ D.M) (hPJ : P ≤ normalizer (jOf D.T : Set G)) (hP : IsPGroup p P) :
    P ⊓ centralizer (proofE D : Set G) ≤ centralizer (D.U : Set G) := fun x hx =>
  uc22p2251f_mem_centralizer D Ch h3 hH c hNb hS3 hbad hp hp5 (hPM hx.1) (hP.to_le (zpowers_le.2 hx.1))
    (hPJ hx.1) hx.2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
