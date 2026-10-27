module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
import CFSG.GroupTheory.PRankBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms

private def s16t3_subgroupMulEquivOfEq {G : Type} [Group G] {H K : Subgroup G} (h : H = K) :
    ↥H ≃* ↥K where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

private theorem s16t3_exists_proj {G : Type} [Group G] {A B : Subgroup G}
    (hAB : B ≤ Subgroup.centralizer (A : Set G)) (hdisj : A ⊓ B = ⊥) :
    ∃ φ : ↥(A ⊔ B) →* ↥B, Function.Surjective φ := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAB hb)) a ha
  have hc : ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  let ψ : ↥A × ↥B →* G := MonoidHom.noncommCoprod A.subtype B.subtype hc
  have hψ : ∀ (m : ↥A) (n : ↥B), ψ (m, n) = (m : G) * (n : G) :=
    fun m n => MonoidHom.noncommCoprod_apply _ _ _ (m, n)
  have hinj : Function.Injective ψ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    rw [hψ, hψ] at h
    have h1 : (a₁ : G)⁻¹ * (a₂ : G) = (b₁ : G) * (b₂ : G)⁻¹ := by
      calc (a₁ : G)⁻¹ * (a₂ : G)
          = (a₁ : G)⁻¹ * (a₂ * b₂) * (b₂ : G)⁻¹ := by group
        _ = (a₁ : G)⁻¹ * (a₁ * b₁) * (b₂ : G)⁻¹ := by rw [← h]
        _ = (b₁ : G) * (b₂ : G)⁻¹ := by group
    have hA : (a₁ : G)⁻¹ * (a₂ : G) ∈ A := mul_mem (inv_mem a₁.2) a₂.2
    have hB : (a₁ : G)⁻¹ * (a₂ : G) ∈ B := by
      rw [h1]; exact mul_mem b₁.2 (inv_mem b₂.2)
    have hbot : (a₁ : G)⁻¹ * (a₂ : G) ∈ (A ⊓ B : Subgroup G) := ⟨hA, hB⟩
    rw [hdisj, Subgroup.mem_bot] at hbot
    have ha : (a₁ : G) = (a₂ : G) := inv_mul_eq_one.mp hbot
    have hb : (b₁ : G) = (b₂ : G) := by
      have h2 : (b₁ : G) * (b₂ : G)⁻¹ = 1 := h1 ▸ hbot
      exact mul_inv_eq_one.mp h2
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hmem : ∀ x, ψ x ∈ A ⊔ B := by
    rintro ⟨a, b⟩
    rw [hψ a b]
    exact Subgroup.mul_mem_sup a.2 b.2
  let ψ' : ↥A × ↥B →* ↥(A ⊔ B) := ψ.codRestrict (A ⊔ B) hmem
  have hsurj : Function.Surjective ψ' := by
    have hrange : A ⊔ B ≤ ψ.range :=
      sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), by rw [hψ]; simp⟩)
        (fun b hb => ⟨(1, ⟨b, hb⟩), by rw [hψ]; simp⟩)
    intro y
    obtain ⟨p, hp⟩ := hrange y.2
    exact ⟨p, Subtype.ext (by change (ψ p : G) = (y : G); exact hp)⟩
  have hinj' : Function.Injective ψ' :=
    (MonoidHom.injective_codRestrict ψ (A ⊔ B) hmem).mpr hinj
  let e : ↥A × ↥B ≃* ↥(A ⊔ B) := MulEquiv.ofBijective ψ' ⟨hinj', hsurj⟩
  exact ⟨(MonoidHom.snd ↥A ↥B).comp e.symm.toMonoidHom, fun b => ⟨e (1, b), by simp⟩⟩

private theorem s16t3_pRank_mulAut_le_of_dvd {X : Type} [Group X] [Finite X] {k N : ℕ}
    (hdvd : Nat.card (MulAut X) ∣ N) (hN : ¬ 3 ^ (k + 1) ∣ N) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ k := by
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (p := 3) (k := k) (by norm_num)
    (H := ⊤) ?_
  rw [Subgroup.card_top]
  exact fun h => hN (h.trans hdvd)

private theorem s16t3_conj_injective {S : Type} [Group S] (hz : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxc : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut S => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * x = (x * g * x⁻¹) * x := by rw [h1]
      _ = x * g := by group
  rw [hz, Subgroup.mem_bot] at hxc
  exact hxc

private theorem s16t3_card_mulAut_dvd_two {S : Type} [Group S] [Finite S]
    (hz : Subgroup.center S = ⊥) (h : Nat.card (MulAut S) ≤ 2 * Nat.card S) :
    Nat.card (MulAut S) ∣ 2 * Nat.card S := by
  have hinj := s16t3_conj_injective hz
  have hdvd : Nat.card S ∣ Nat.card (MulAut S) := by
    have h1 : Nat.card S = Nat.card (MonoidHom.range (MulAut.conj : S →* MulAut S)) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨d, hd⟩ := hdvd
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hd2 : d ≤ 2 := by
    have h' : Nat.card S * d ≤ Nat.card S * 2 := by
      calc Nat.card S * d = Nat.card (MulAut S) := hd.symm
        _ ≤ 2 * Nat.card S := h
        _ = Nat.card S * 2 := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h' hSpos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    have hpos : 0 < Nat.card (MulAut S) := Nat.card_pos
    omega
  rw [hd]
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · exact ⟨2, by ring⟩
  · exact ⟨1, by ring⟩

private theorem s16t3_card_mulAut_dvd_of_outer {S : Type} [Group S] {k : ℕ}
    (hz : Subgroup.center S = ⊥) (hk : Nat.card (Outer S) ∣ k) :
    Nat.card (MulAut S) ∣ k * Nat.card S := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  have hinj := s16t3_conj_injective hz
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) =
      Nat.card S := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [h, hinner]
  exact Nat.mul_dvd_mul_right hk _

private theorem s16t3_center_eq_bot_of_isAlt {X : Type} [Group X] {n : ℕ} (h : IsAlt X n)
    (hn : 4 ≤ n) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have hmap : (Subgroup.center X).map e.toMonoidHom =
      Subgroup.center (alternatingGroup (Fin n)) := by
    simpa using Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn)] at hmap
  rwa [Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center X) (f := e.toMonoidHom)
    e.injective] at hmap

private theorem s16t3_pRank_three_alt_five {X : Type} [Group X] [Finite X] (h : IsAlt X 5) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  have hcard : Nat.card X = 60 := by
    rw [s15k_six_alt_card h (by norm_num)]; norm_num [Nat.factorial]
  have hz := s16t3_center_eq_bot_of_isAlt h (by norm_num)
  have hdvd := s16t3_card_mulAut_dvd_two hz (s15k_six_alt h (Or.inl rfl)).2
  rw [hcard] at hdvd
  exact s16t3_pRank_mulAut_le_of_dvd (k := 1) hdvd (by norm_num)

private theorem s16t3_pRank_three_alt_six {X : Type} [Group X] [Finite X] (h : IsAlt X 6) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  have hcard : Nat.card X = 360 := by
    rw [s15k_six_alt_card h (by norm_num)]; norm_num [Nat.factorial]
  have hz := s16t3_center_eq_bot_of_isAlt h (by norm_num)
  obtain ⟨e⟩ := h
  have hout : Nat.card (Outer X) ∣ 4 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    rcases s15k_six_alt6_outer with h2 | h4
    · rw [h2]; norm_num
    · rw [h4]
  have hdvd := s16t3_card_mulAut_dvd_of_outer hz hout
  rw [hcard] at hdvd
  exact s16t3_pRank_mulAut_le_of_dvd (k := 2) hdvd (by norm_num)

private theorem s16t3_pRank_three_alt_seven {X : Type} [Group X] [Finite X] (h : IsAlt X 7) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  have hcard : Nat.card X = 2520 := by
    rw [s15k_six_alt_card h (by norm_num)]; norm_num [Nat.factorial]
  have hz := s16t3_center_eq_bot_of_isAlt h (by norm_num)
  have hdvd := s16t3_card_mulAut_dvd_two hz (s15k_six_alt h (Or.inr (by norm_num))).2
  rw [hcard] at hdvd
  exact s16t3_pRank_mulAut_le_of_dvd (k := 2) hdvd (by norm_num)

private theorem s16t3_pRank_three_sln_three {X : Type} [Group X] [Finite X]
    (h : IsSLn X 3 1) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  have hLn : IsLn X 3 1 := s16k_isLn_of_isSLn (by norm_num) h
  exact s16t3_pRank_mulAut_le_of_dvd (k := 1) (card_mulAut_dvd_of_isL3 hLn) (by norm_num)

private theorem s16t3_pRank_three_sln_four {X : Type} [Group X] [Finite X]
    (h : IsSLn X 4 1) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  have hLn : IsLn X 4 1 := s16k_isLn_of_isSLn (by norm_num) h
  have hcard : Nat.card X = 20160 := (s15k_six_l4 hLn).1
  have hAlt : IsAlt X 8 :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hLn
  have hz := s16t3_center_eq_bot_of_isAlt hAlt (by norm_num)
  have hdvd := s16t3_card_mulAut_dvd_two hz
    (s15k_six_alt hAlt (Or.inr (by norm_num))).2
  rw [hcard] at hdvd
  exact s16t3_pRank_mulAut_le_of_dvd (k := 2) hdvd (by norm_num)

private theorem s16t3_pRank_three_omegaMinus_four {X : Type} [Group X] [Finite X]
    (h : IsOmegaMinus X 4 1) : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 1 :=
  s16t3_pRank_three_alt_five (s16k_isAlt_five_of_isOmegaMinus_four h)

private theorem s16t3_exists_normal_card_seven {Q : Type} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 21) : ∃ P : Subgroup Q, P.Normal ∧ Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 Q) := inferInstance
  have hP : Nat.card (P : Subgroup Q) = 7 := by
    rw [Sylow.card_eq_multiplicity, hQ, show (21 : ℕ) = 7 * 3 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hidx : (P : Subgroup Q).index = 3 := by
    have := (P : Subgroup Q).card_mul_index
    rw [hP, hQ] at this
    omega
  have hmod := card_sylow_modEq_one 7 Q
  have hdvd : Nat.card (Sylow 7 Q) ∣ 3 := hidx ▸ P.card_dvd_index
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have : Subsingleton (Sylow 7 Q) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨P, Sylow.normal_of_subsingleton P, hP⟩
  · rw [h3] at hmod
    exact absurd hmod (by decide)

theorem ThreeNat.pRank_three_le_two {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    (hL : ((IsSLn ↥L 3 1 ∨ UC22.IsAlt ↥L 5 ∨ IsOmegaMinus ↥L 4 1) ∧
        (Nat.card ↥(s1t3KBar A L) = 7 ∨ Nat.card ↥(s1t3KBar A L) = 168)) ∨
      ((IsSLn ↥L 4 1 ∨ UC22.IsAlt ↥L 6 ∨ UC22.IsAlt ↥L 7) ∧ Nat.card ↥(s1t3KBar A L) = 7)) :
    CFSG.Open.pRank 3 A ≤ 2 := by
  obtain ⟨N, hNA, -, -, hcomm, hdisj, hsup, -⟩ := h.structure_of_seven h7
  have hKN : s1t3KBar A L ≤ Subgroup.centralizer (N : Set (MulAut W)) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact hcomm n hn k hk
  have hrank : CFSG.Open.pRank 3 A =
      CFSG.Open.pRank 3 N + CFSG.Open.pRank 3 (s1t3KBar A L) := by
    have h := s13_pRank_sup_eq_add (p := 3) (by norm_num) hKN hdisj
    rw [hsup] at h
    exact h
  let g : ↥N →* ↥(Subgroup.normalizer (L : Set (MulAut W))) :=
    { toFun := fun x => ⟨x.1, h.normal (hNA x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let f : ↥N →* MulAut ↥L := (L.normalizerMonoidHom).comp g
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    have hx' : g x ∈ (L.normalizerMonoidHom).ker :=
      (MonoidHom.mem_ker).mpr (show L.normalizerMonoidHom (g x) = 1 from hx)
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hx'
    have hxK : (x : MulAut W) ∈ s1t3KBar A L :=
      ⟨hNA x.2, hx'⟩
    have hxbot : (x : MulAut W) ∈ N ⊓ s1t3KBar A L := ⟨x.2, hxK⟩
    rw [hdisj, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot
  have hNle : CFSG.Open.pRank 3 N ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup N]
    exact CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) f hinj
  have hK7 : Nat.card ↥(s1t3KBar A L) = 7 →
      CFSG.Open.pRank 3 (s1t3KBar A L) ≤ 0 := fun hc =>
    CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (p := 3) (k := 0) (H := s1t3KBar A L)
      (by norm_num) (by rw [hc]; norm_num)
  have hK168 : Nat.card ↥(s1t3KBar A L) = 168 →
      CFSG.Open.pRank 3 (s1t3KBar A L) ≤ 1 := fun hc =>
    CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (p := 3) (k := 1) (H := s1t3KBar A L)
      (by norm_num) (by rw [hc]; norm_num)
  rcases hL with ⟨hshape, hKord⟩ | ⟨hshape, hK7'⟩
  · have hN1 : CFSG.Open.pRank 3 N ≤ 1 := by
      rcases hshape with hsl | hal | hom
      · exact hNle.trans (s16t3_pRank_three_sln_three hsl)
      · exact hNle.trans (s16t3_pRank_three_alt_five hal)
      · exact hNle.trans (s16t3_pRank_three_omegaMinus_four hom)
    rcases hKord with hk | hk
    · have hk0 := hK7 hk
      omega
    · have hk1 := hK168 hk
      omega
  · have hN2 : CFSG.Open.pRank 3 N ≤ 2 := by
      rcases hshape with hsl | hal | ha7
      · exact hNle.trans (s16t3_pRank_three_sln_four hsl)
      · exact hNle.trans (s16t3_pRank_three_alt_six hal)
      · exact hNle.trans (s16t3_pRank_three_alt_seven ha7)
    have hk0 := hK7 hK7'
    omega

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem Setting16.false_of_kBar_order_21_of_opRes
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hset : Setting16 D V₀ V L) (hop : UC22.F10.OpRes 3 D.M = D.M)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV)
      (lBar V₀ V hV L)) = 21) : False := by
  obtain ⟨N, hNA, -, -, hcomm, hdisj, hsup, -⟩ := hT.structure_of_seven h7
  have hKN : s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤
      Subgroup.centralizer (N : Set (MulAut (Vtil V₀ V hV))) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact hcomm n hn k hk
  obtain ⟨φ₀, hφ₀⟩ := s16t3_exists_proj hKN hdisj
  let eA : ↥(N ⊔ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) ≃*
      ↥(Mbar D.M V₀ V hV) := s16t3_subgroupMulEquivOfEq hsup
  let φ : ↥(Mbar D.M V₀ V hV) →*
      ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) :=
    φ₀.comp eA.symm.toMonoidHom
  have hφ : Function.Surjective φ := hφ₀.comp eA.symm.surjective
  obtain ⟨P, hPnorm, hPcard⟩ := s16t3_exists_normal_card_seven hK
  haveI : P.Normal := hPnorm
  have hPidx : P.index = 3 := by
    have hc := P.card_mul_index
    rw [hPcard, hK] at hc
    omega
  let N₂ : Subgroup ↥(Mbar D.M V₀ V hV) := P.comap φ
  have hN₂idx : N₂.index = 3 := by
    rw [Subgroup.index_comap_of_surjective P hφ, hPidx]
  haveI : N₂.Normal := Subgroup.normal_comap φ
  exact s16e_mbar_index_ne_three_of_opRes D hop hset.hyp16 hV N₂ hN₂idx

theorem Setting16.false_of_kBar_order_21
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hset : Setting16 D V₀ V L) (h638 : UC6.R6_38 D)
    (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV)
      (lBar V₀ V hV L)) = 21) : False :=
  hset.false_of_kBar_order_21_of_opRes
    (h638 3 Nat.prime_three (by norm_num) (Or.inl h3)) hT h7 hK

theorem S16gRowCtx.false_of_kBar_order_21 (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 21) : False :=
  h.setting.false_of_kBar_order_21 h.std.h638 h3 hT h7 hK

theorem S16gRowCtx.false_of_count (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL : ((IsSLn ↥(lBar V₀ V hV L) 3 1 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 5 ∨
          IsOmegaMinus ↥(lBar V₀ V hV L) 4 1) ∧
        (Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7 ∨
          Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168)) ∨
      ((IsSLn ↥(lBar V₀ V hV L) 4 1 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨
          UC22.IsAlt ↥(lBar V₀ V hV L) 7) ∧
        Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7)) : False := by
  have h1 := h.three_le_pRank h3
  have h2 := hT.pRank_three_le_two h7 hL
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
