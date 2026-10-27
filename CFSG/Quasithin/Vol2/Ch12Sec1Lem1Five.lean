module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1E9
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Kv
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Syl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped Matrix

namespace Sec1211Ns

variable {G : Type} [Group G]

theorem odd_mem_normalizer_of_cases {H K : Subgroup G} (hKH : K ≤ H)
    (h : (K.subgroupOf H).Normal ∨ (conjSubgroupsBy H K).ncard = 2) {x : G} (hxH : x ∈ H)
    (hx : Odd (orderOf x)) : x ∈ Subgroup.normalizer (K : Set G) := by
  rcases h with hn | hc
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn hxH
  by_cases hxK : x ∈ Subgroup.normalizer (K : Set G)
  · exact hxK
  have hx2 : x ^ 2 ∈ Subgroup.normalizer (K : Set G) := by
    obtain ⟨A, B, hAB, hS⟩ := Set.ncard_eq_two.mp hc
    have hmem : ∀ t ∈ H, K.map (MulAut.conj t).toMonoidHom = A ∨
        K.map (MulAut.conj t).toMonoidHom = B := fun t ht => by
      have : K.map (MulAut.conj t).toMonoidHom ∈ conjSubgroupsBy H K := ⟨t, ht, rfl⟩
      rw [hS] at this
      exact this
    have hconj : ∀ s t : G, (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
        K.map (MulAut.conj (s * t)).toMonoidHom := fun s t => by
      rw [Subgroup.map_map, map_mul]
      rfl
    have h1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by ext y; simp
    have hne : K.map (MulAut.conj x).toMonoidHom ≠ K := fun h => hxK (A38.map_conj_eq_iff.mp h)
    have hne2 : K.map (MulAut.conj (x ^ 2)).toMonoidHom ≠ K.map (MulAut.conj x).toMonoidHom := by
      intro h
      apply hne
      have h2 := congrArg (fun J : Subgroup G => J.map (MulAut.conj x⁻¹).toMonoidHom) h
      simp only [hconj] at h2
      rwa [pow_two, inv_mul_cancel_left, inv_mul_cancel, h1] at h2
    have hK1 := hmem 1 H.one_mem
    have hKx := hmem x hxH
    have hKx2 := hmem (x ^ 2) (H.pow_mem hxH 2)
    rw [h1] at hK1
    refine A38.map_conj_eq_iff.mp ?_
    rcases hK1 with h | h <;> rcases hKx with h' | h' <;> rcases hKx2 with h'' | h''
    · exact absurd (h'.trans h.symm) hne
    · exact absurd (h'.trans h.symm) hne
    · exact h''.trans h.symm
    · exact absurd (h''.trans h'.symm) hne2
    · exact absurd (h''.trans h'.symm) hne2
    · exact h''.trans h.symm
    · exact absurd (h'.trans h.symm) hne
    · exact absurd (h'.trans h.symm) hne
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 2) (x := x)
    (Nat.coprime_two_left.mpr hx)
  rw [← hm]
  exact Subgroup.pow_mem _ hx2 m

variable [Finite G]

theorem le_of_map_ne_bot {X N : Subgroup G} {Sg : Type} [Group Sg] [IsSimpleGroup Sg]
    (hX : ⁅X, X⁆ = X) (f : ↥X →* Sg) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hNX : N ≤ X) (hNn : ∀ l ∈ X, ∀ x ∈ N, l * x * l⁻¹ ∈ N)
    (hne : ∃ x : ↥X, (x : G) ∈ N ∧ f x ≠ 1) : X ≤ N := by
  have hNnormal : (N.subgroupOf X).Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNn l l.2 x hx⟩
  have hfP : ((N.subgroupOf X).map f).Normal := Subgroup.Normal.map hNnormal f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf X).map f) with h | h
  · exfalso
    obtain ⟨x, hxN, hfx⟩ := hne
    apply hfx
    have : f x ∈ (N.subgroupOf X).map f := ⟨x, hxN, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · refine Sec1216Lv.perfect_le_of_le_sup_two hX hNX hNn (hker.map X.subtype)
      (Subgroup.map_subtype_le _) ?_
    intro x hx
    have hfx : f ⟨x, hx⟩ ∈ (N.subgroupOf X).map f := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨p, hp, hpx⟩ := hfx
    have hk : p⁻¹ * ⟨x, hx⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
    have e : x = (p : G) * ((p⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hp ⟨_, hk, rfl⟩

namespace Setting

variable {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G} {S : Setting T L V V₁ V₂ n a₀ c₀}

theorem lv_le_of_isComponentIn_five (F : Frame S 4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({a₀ * c₀} : Set G))) (hOut : OutSolvable ↥K) :
    Sec1216Lv.lv L (a₀ * c₀) ≤ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := S.hyp.simple
  have hqtke : QTKECore G := qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  set Y := Sec1216Lv.lv L (a₀ * c₀) with hY
  have hYH : Y ≤ H := Sec1216Lv.lv_le_centralizer L _
  have hYp : ⁅Y, Y⁆ = Y := Sec1216Lv.lv_perfect L _
  have hKc : K ∈ cComp H := Sec1216Lv.cComp_of_isComponentIn hK
  have hKH : K ≤ H := hK.1
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := by
    have h3 := Vol2Native.lemma_1_2_1_three hqtke.1 h37 h38 S.pCoreOf_ne_bot hKc
    refine (C2Nine.opResidual_eq_of_perfect hYp).symm.le.trans ?_
    show Subgroup.closure {x | x ∈ Y ∧ (orderOf x).Coprime 2} ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxY, hxc⟩
    exact odd_mem_normalizer_of_cases hKH (h3.imp_right And.left) (hYH hxY)
      (Nat.coprime_two_right.mp hxc)
  set ψ := psi F S.lv_le_Xv with hψdef
  have hψs : Function.Surjective ψ := psi_lv_surjective F
  have hψk : IsPGroup 2 ψ.ker := isPGroup_ker_psi_lv F
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    Vol2Native.A312L.sl_isSimple_of_card_two (Nat.card_zmod 2) (by norm_num)
  by_contra hYK
  have hYK1 : ∀ y : ↥Y, (y : G) ∈ K → ψ y = 1 := by
    intro y hy
    by_contra h1
    apply hYK
    refine (le_of_map_ne_bot (N := Y ⊓ K) hYp ψ hψs hψk inf_le_left (fun l hl x hx =>
      ⟨Y.mul_mem (Y.mul_mem hl hx.1) (Y.inv_mem hl),
        (Subgroup.mem_normalizer_iff.mp (hYN hl) x).mp hx.2⟩) ⟨y, ⟨y.2, hy⟩, h1⟩).trans
      inf_le_right
  have hYC1 : ∀ y : ↥Y, (y : G) ∈ Subgroup.centralizer (K : Set G) → ψ y = 1 := by
    intro y hy
    by_contra h1
    have hYC := (le_of_map_ne_bot (N := Y ⊓ Subgroup.centralizer (K : Set G)) hYp ψ hψs hψk
      inf_le_left (fun l hl x hx =>
      ⟨Y.mul_mem (Y.mul_mem hl hx.1) (Y.inv_mem hl),
        (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer K (hYN hl)) x).mp
          hx.2⟩) ⟨y, ⟨y.2, hy⟩, h1⟩).trans inf_le_right
    obtain ⟨u, huW, huV, hu1, huU, hus⟩ := S.exists_singular
    have hulv : u ∈ Y := sup_le S.W₁_le_lv S.W₂_le_lv huW
    apply S.not_le_centralizer huV hu1 huU hus hK
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hYC hulv) k hk
  obtain ⟨P, hPY, hP9, hPe, hPinj⟩ := E9.exists_e9 ψ hψs hψk
  have hPK : ∀ x ∈ P, x ∈ K → x = 1 := fun x hx hxK =>
    congrArg Subtype.val (hPinj ⟨x, hPY hx⟩ hx (hYK1 ⟨x, hPY hx⟩ hxK))
  have hPC : ∀ x ∈ P, x ∈ Subgroup.centralizer (K : Set G) → x = 1 := fun x hx hxC =>
    congrArg Subtype.val (hPinj ⟨x, hPY hx⟩ hx (hYC1 ⟨x, hPY hx⟩ hxC))
  obtain ⟨x₀, hx₀P, hx₀1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : P = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
    rw [h1, Subgroup.card_bot] at hP9
    omega
  have h3K : 3 ∣ Nat.card K := by
    by_contra h3
    have hx₀Y := hPY hx₀P
    let φ : ↥Y →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hYN)
    have hφ : ∀ (γ : ↥Y) (k : ↥K), ((φ γ k : ↥K) : G) = (γ : G) * (k : G) * (γ : G)⁻¹ := by
      intro γ k
      simp [φ]
    have hYperf : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYp
    obtain ⟨k, hk⟩ := A38.exists_inner_of_outSolvable hOut hYperf φ ⟨x₀, hx₀Y⟩
    have hc : (k : G)⁻¹ * x₀ ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨j, hj⟩ : ↥K) : G)) hk
      simp only [hφ, MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
      calc j * ((k : G)⁻¹ * x₀) = (k : G)⁻¹ * ((k : G) * j * (k : G)⁻¹) * x₀ := by group
        _ = (k : G)⁻¹ * (x₀ * j * x₀⁻¹) * x₀ := by rw [h1]
        _ = (k : G)⁻¹ * x₀ * j := by group
    set c := (k : G)⁻¹ * x₀ with hcdef
    have hkc : Commute (k : G) c := (Subgroup.mem_centralizer_iff.mp hc k k.2)
    have hx₀ : x₀ = k * c := by rw [hcdef]; group
    have hk3 : (k : G) ^ 3 ∈ Subgroup.centralizer (K : Set G) := by
      have h1 : (k : G) ^ 3 * c ^ 3 = 1 := by
        rw [← hkc.mul_pow, ← hx₀]
        exact hPe.2 x₀ hx₀P
      have h2 : (k : G) ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 3)
    have hcop : Nat.Coprime 3 (orderOf (k : G)) := by
      rw [Subgroup.orderOf_coe]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h =>
        h3 (h.trans (orderOf_dvd_natCard k))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hkC : (k : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [← hm]
      exact Subgroup.pow_mem _ hk3 m
    exact hx₀1 (hPC x₀ hx₀P (by rw [hx₀]; exact Subgroup.mul_mem _ hkC hc))
  have hPN : P ≤ Subgroup.normalizer (K : Set G) := hPY.trans hYN
  let φ₀ : ↥P →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hPN)
  let _ : MulAction ↥P ↥K := MulAction.compHom ↥K φ₀
  have hsmul : ∀ (p : ↥P) (k : ↥K), ((p • k : ↥K) : G) = (p : G) * (k : G) * (p : G)⁻¹ := by
    intro p k
    rfl
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hmod := hP3.card_modEq_card_fixedPoints ↥K
  set C := K ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCcard : Nat.card ↥C = Nat.card (MulAction.fixedPoints ↥P ↥K) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨c, c.2.1⟩, fun p => Subtype.ext ?_⟩
        invFun := fun k => ⟨k.1, k.1.2, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
        left_inv := fun c => rfl
        right_inv := fun k => rfl }
    · rw [hsmul]
      show (p : G) * (c : G) * (p : G)⁻¹ = c
      rw [Subgroup.mem_centralizer_iff.mp c.2.2 p p.2, mul_inv_cancel_right]
    · have h1 := congrArg Subtype.val (k.2 ⟨p, hp⟩)
      rw [hsmul] at h1
      calc p * (k.1 : G) = (p : G) * k.1 * p⁻¹ * p := by group
        _ = k.1 * p := by rw [h1]
  have h3C : 3 ∣ Nat.card ↥C := by
    rw [hCcard]
    exact (hmod.dvd_iff dvd_rfl).mp h3K
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3C
  have hz3 : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
  have hz3' : (z : G) ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one _
  have hzK : (z : G) ∈ K := z.2.1
  have hzP : ∀ p ∈ P, p * z = z * p := fun p hp => Subgroup.mem_centralizer_iff.mp z.2.2 p hp
  have hcommPZ : ∀ (p : ↥P) (w : ↥(Subgroup.zpowers (z : G))),
      Commute (P.subtype p) ((Subgroup.zpowers (z : G)).subtype w) := by
    rintro p ⟨w, hw⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right (hzP p p.2) i)
  set f := P.subtype.noncommCoprod (Subgroup.zpowers (z : G)).subtype hcommPZ with hfdef
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, w⟩ h
    have h1 : (p : G) * w = 1 := h
    have hwK : (w : G) ∈ K := (Subgroup.zpowers_le.mpr hzK) w.2
    have hp1 : (p : G) = 1 := by
      have hpw : (p : G) = (w : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact hPK p p.2 (by rw [hpw]; exact K.inv_mem hwK)
    have hw1 : (w : G) = 1 := by rw [hp1, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hw1)
  have hcard : Nat.card (↥P × ↥(Subgroup.zpowers (z : G))) = 3 ^ 3 := by
    rw [Nat.card_prod, hP9, Nat.card_zpowers, hz3]
    norm_num
  have hle : 3 ≤ CFSG.Open.pRank 3 H := by
    refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => ?_) (fun a => ?_)
      hcard f hf ?_
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact congrArg Subtype.val (hPe.1.1.comm a.1 b.1)
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
        show (a.2 : G) * b.2 = b.2 * a.2
        rw [← hi, ← hj]
        exact ((Commute.refl (z : G)).zpow_zpow i j).eq
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (a.1 : G) ^ 3 = 1
        exact hPe.2 _ a.1.2
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
      show (a.2 : G) ^ 3 = 1
      rw [← hi, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        hz3', _root_.one_zpow]
    · rintro _ ⟨⟨p, w⟩, rfl⟩
      show (p : G) * w ∈ H
      exact H.mul_mem (hYH (hPY p.2)) (hKH ((Subgroup.zpowers_le.mpr hzK) w.2))
  have h2 : CFSG.Open.pRank 3 H ≤ 2 := pRank_le_two_of_pCoreOf_ne_bot S.hyp.qtke S.pCoreOf_ne_bot
    Nat.prime_three (by norm_num)
  omega

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
