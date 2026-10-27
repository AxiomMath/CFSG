module

public import CFSG.Quasithin.H13.L32NItems14324
public import CFSG.Quasithin.H13.L32NLem14323
public import CFSG.Quasithin.H13.L32NLem1434
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat
public import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14323

variable {G : Type} [Group G]

theorem card_hat_eq {U : Subgroup G} (D : HatModelU U) {A : Subgroup G} (hA : A ≤ U) :
    Nat.card ↥(D.hat A) = Nat.card (D.homOn hA).range := by
  refine Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.ofAdd v.1, ?_⟩
      invFun := fun x => ⟨Multiplicative.toAdd x.1, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun x => rfl }
  · obtain ⟨a, haA, -, hav⟩ := (L128A.HatU.mem_hat D).1 v.2
    exact ⟨⟨a, haA⟩, by rw [← hav]; rfl⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    rw [← ha]
    exact L128A.HatU.π_mem_hat D a.2 (hA a.2)

theorem card_submodule {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (S : Submodule (ZMod 2) W) : Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S), Nat.card_zmod]

def stabHat {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (S : Submodule (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {γ | ∀ w ∈ S, γ w ∈ S}
  mul_mem' {γ δ} hγ hδ w hw := hγ _ (hδ w hw)
  one_mem' w hw := hw
  inv_mem' {γ} hγ := by
    intro w hw
    have := Finite.of_injective (fun v : ↥S => (v : W)) Subtype.val_injective
    let f : ↥S → ↥S := fun v => ⟨γ v, hγ v v.2⟩
    have hf : Function.Injective f := fun v v' h => Subtype.ext (γ.injective (congrArg
      Subtype.val h))
    obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
    have hv' : γ v = w := congrArg Subtype.val hv
    have e1 : γ⁻¹ w = v := by
      rw [← hv', ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rw [e1]
    exact v.2

end L14323

theorem lemma14323Parts_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11)
    (h12811h : Lemma12_8_11_hat) (h12813 : Lemma12_8_13) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Module.finrank (ZMod 2) D.V = 4 →
      (D.hat V = D.hat (l32nE T V V₂ g) ∧ Nat.card ↥(D.hat V) = 4) ∧
      ((D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
          (D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ∧
        ∀ x ∈ D.img (CFSG.conjugate (centerOf (fsuU T V)) g), ∀ v ∈ D.hat V, x v = v) ∧
      (l32nH T V ⊓ Subgroup.normalizer (L : Set G)) ⊔ l32nCHat T V < l32nH T V := by
  intro G _ _ T L V h V₂ g hV₂ hgP hgN D hd
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨-, hE, -⟩ := h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  obtain ⟨hVE, hZV, -, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  have hVZ := lemma12_8_8_three h1222 h12213 hs
  obtain ⟨-, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  set E := l32nE T V V₂ g with hEdef
  have hEU : E ≤ fsuU T V := inf_le_left.trans inf_le_left
  have hVU : V ≤ fsuU T V := hVE.trans hEU
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVhat : Nat.card ↥(D.hat V) = 4 := by
    rw [L14323.card_hat_eq D hVU]
    have h1 := D.card_eq_mul_range hVU
    rw [hVZ, hV8, hV1] at h1
    omega
  have hcardV : Nat.card D.V = 16 := by
    have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
    norm_num
  have hiso := card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hEU hEc)
  have hle : D.hat V ≤ D.hat E := L128A.HatU.hat_mono D hVE
  have hrV : Module.finrank (ZMod 2) ↥(D.hat V) = 2 := by
    have h1 := L14323.card_submodule (D.hat V)
    rw [hVhat] at h1
    have h2 : (2 : ℕ) ^ 2 = 2 ^ Module.finrank (ZMod 2) ↥(D.hat V) := by rw [← h1]; norm_num
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  have hrE : Module.finrank (ZMod 2) ↥(D.hat E) = 2 := by
    have h1 := L14323.card_submodule (D.hat E)
    have h2 : Nat.card ↥(D.hat E) ≤ 4 := by
      rw [hcardV, pow_two] at hiso
      by_contra hc
      have hc' : 5 ≤ Nat.card ↥(D.hat E) := by omega
      have := Nat.mul_le_mul hc' hc'
      omega
    have h3 : 2 ^ Module.finrank (ZMod 2) ↥(D.hat E) ≤ 2 ^ 2 := by rw [← h1]; simpa using h2
    have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
    have h5 := Submodule.finrank_mono hle
    omega
  have hVEq : D.hat V = D.hat E :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrV, hrE])
  refine ⟨⟨hVEq, hVhat⟩, ⟨?_, ?_⟩, ?_⟩
  · have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
    have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by
      rw [he] at hV1; omega
    obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
    obtain ⟨-, h5, -⟩ := h12811h G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN a haV₂ ha1 D
    rw [hrE, hd] at h5
    change 2 + Nat.log 2 ((D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
        (D.img (CFSG.conjugate (l32nW T V V₂) g))) = 4 - 1 at h5
    have hlog : Nat.log 2 ((D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
        (D.img (CFSG.conjugate (l32nW T V V₂) g))) = 1 := by omega
    have hUT : fsuU T V ≤ T := (hs.almostSpecial h1222 h12213).G22_three.1
    have hT2 : IsPGroup 2 ↥T := hs.hyp.hyp.sylow.1
    have hX2 : IsPGroup 2 ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := by
      intro x
      obtain ⟨y, hyX, hyN, hyx⟩ := (L128A.HatU.mem_img D).1 x.2
      obtain ⟨w, hw, hwy⟩ := hyX
      obtain ⟨k, hk⟩ := hT2 ⟨w, hUT hw.1⟩
      have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hy : y ^ 2 ^ k = 1 := by
        rw [← hwy, ← map_pow, hk', map_one]
      refine ⟨k, Subtype.ext ?_⟩
      have e1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ 2 ^ k = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hy)
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyx, ← map_pow, e1, map_one]
    have : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
      Finite.of_injective (fun e : D.V ≃ₗ[ZMod 2] D.V => (e : D.V → D.V))
        (fun a b hab => LinearEquiv.ext (congrFun hab))
    have hdvd : (D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
        (D.img (CFSG.conjugate (l32nW T V V₂) g)) ∣
          Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) :=
      Subgroup.relIndex_dvd_card _ _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hX2
    rw [hn] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj, Nat.log_pow (by norm_num)] at hlog
    rw [hj, hlog, pow_one]
  · intro x hx v hv
    obtain ⟨y, hyZ, hyN, rfl⟩ := (L128A.HatU.mem_img D).1 hx
    obtain ⟨b, hbV, -, rfl⟩ := (L128A.HatU.mem_hat D).1 hv
    rw [D.ρ_π ⟨y, hyN⟩ b (hVU hbV)]
    have hc := Subgroup.mem_centralizer_iff.mp (hZV hyZ) b hbV
    show D.π (y * b * y⁻¹) = D.π b
    rw [← hc, mul_inv_cancel_right]
  · have hV1V : fsuV1 T V ≤ V := inf_le_left
    have hV1ne : fsuV1 T V ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hV1
      norm_num at hV1
    have h1433 := lemma1433Six_of_inputs h1332 h1334 h1222 G T L V h.hyp h.fsu (fsuV1 T V)
      (l32nH T V) hV1V hV1ne le_rfl
    have hCH : l32nCHat T V ≤ l32nH T V := fun x hx => hx.1
    refine lt_of_le_of_ne (sup_le inf_le_left hCH) fun heq => ?_
    have hHN : l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
      le_normalizer_conjClosure V _
    have hAN : l32nH T V ⊓ Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer (fsuU T V : Set G) := inf_le_left.trans hHN
    have hmaps : D.img (l32nH T V) ≤ L14323.stabHat (D.hat V) := by
      have himg : D.img (l32nH T V) = D.img (l32nH T V ⊓ Subgroup.normalizer (V : Set G)) ⊔
          D.img (l32nCHat T V) := by
        conv_lhs => rw [← heq, h1433]
        unfold HatModelU.img
        rw [Subgroup.subgroupOf_sup hAN (hCH.trans hHN), Subgroup.map_sup]
      rw [himg]
      refine sup_le ?_ ?_
      · intro γ hγ w hw
        obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
        obtain ⟨b, hbV, hbU, rfl⟩ := (L128A.HatU.mem_hat D).1 hw
        rw [D.ρ_π ⟨x, hxN⟩ b hbU]
        have hxb : x * b * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hx.2 b).mp hbV
        exact L128A.HatU.π_mem_hat D hxb (hVU hxb)
      · intro γ hγ w hw
        obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
        rw [(L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).2 hx.2.2]
        exact hw
    have hU : ∀ u ∈ fsuU T V, D.π u ∈ D.hat V := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨k, hk, v, hv, rfl⟩ := hy
        rw [← D.ρ_π ⟨k, hHN hk⟩ v (hVU hv)]
        exact hmaps (L128A.HatU.rho_mem_img D hk (hHN hk)) _
          (L128A.HatU.π_mem_hat D hv (hVU hv))
      | one => rw [L128A.HatU.π_one]; exact Submodule.zero_mem _
      | mul y y' hy hy' ih ih' =>
        rw [D.π_mul y hy y' hy']
        exact Submodule.add_mem _ ih ih'
      | inv y hy ih =>
        rw [L128A.HatU.π_inv D hy]
        exact Submodule.neg_mem _ ih
    have htop : D.hat V = ⊤ := by
      rw [eq_top_iff]
      intro v _
      obtain ⟨u, hu, rfl⟩ := D.π_surj v
      exact hU u hu
    have h2 : Nat.card ↥(⊤ : Submodule (ZMod 2) D.V) = Nat.card D.V :=
      Nat.card_congr Submodule.topEquiv.toEquiv
    rw [htop, h2, hcardV] at hVhat
    omega

theorem lemma14323Rest_of_two (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11)
    (h12811h : Lemma12_8_11_hat) (h12813 : Lemma12_8_13) (h2 : Lemma14323Two) :
    Lemma14323Rest := by
  intro G _ _ T L V h V₂ g hV₂ hgP hgN D hd
  obtain ⟨h1, h3, h4⟩ := lemma14323Parts_of_inputs h1332 h1334 h1222 h12213 h12811 h12811h
    h12813 G T L V h V₂ g hV₂ hgP hgN D hd
  exact ⟨h1, h2 G T L V h V₂ g hV₂ hgP hgN D hd, h3, h4⟩

theorem lemma14324One_of_big (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11)
    (h12813 : Lemma12_8_13) (h2 : Lemma14323Two) (hBig : Lemma14324Big) : Lemma14324One := by
  intro G _ _ T L V h hlt V₂ g hV₂ hgP hgN D
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  have hGe := lemma14323Ge_of_inputs h1332 h1334 h1222 h12213 h12811 h12813 G T L V h
  rw [D.card_U] at hGe
  have hZpos : 0 < Nat.card ↥(centerOf (fsuU T V)) := Nat.card_pos
  have h16 : 2 ^ 4 ≤ Nat.card D.V := by nlinarith
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h16
  have hd4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h16
  have heven : Even (Module.finrank (ZMod 2) D.V) :=
    LinearMap.BilinForm.IsAlt.even_finrank (fun v => L128A.HatU.B_isAlt D v) D.nondegenerate
  rcases (show Module.finrank (ZMod 2) D.V = 4 ∨ 6 ≤ Module.finrank (ZMod 2) D.V by
    obtain ⟨k, hk⟩ := heven; omega) with hd | hd
  · right
    refine ⟨hd, ?_⟩
    rcases h2 G T L V h V₂ g hV₂ hgP hgN D hd with hi | hii | hiii | hiv
    · exact Or.inl hi
    · exact Or.inr (Or.inl hii)
    · exact Or.inr (Or.inr hiii)
    · exfalso
      obtain ⟨w, -, -, huniq⟩ := centerOrderTwo_of_isQ8Sq hiv.q8
      have key : ∀ x ∈ centerOf (fsuU T V), x = 1 ∨ x = (w : G) := by
        intro x hx
        have hxc : ∀ y : ↥(fsuU T V), (⟨x, hx.1⟩ : ↥(fsuU T V)) * y = y * ⟨x, hx.1⟩ :=
          fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2).symm
        rcases huniq _ hxc with h1 | h1
        · exact Or.inl (congrArg Subtype.val h1)
        · exact Or.inr (congrArg Subtype.val h1)
      obtain ⟨c, hcZ, hcV⟩ := IsConcreteLE.exists_of_lt hlt
      obtain ⟨-, -, -, hV1, -⟩ := stmtL32NModule_of_inputs h1332 h1334 G T L V h.hyp h.fsu
      have hV1ne : fsuV1 T V ≠ ⊥ := fun hb => by
        rw [hb, Subgroup.card_bot] at hV1
        norm_num at hV1
      obtain ⟨⟨z, hzV⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1ne
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      rcases key c hcZ with hc | hc
      · exact hcV (hc ▸ one_mem _)
      rcases key z (hlt.le hzV) with hz | hz
      · exact hz1' hz
      · exact hcV (by rw [hc, ← hz]; exact hzV)
  · left
    exact (hBig G T L V h hlt V₂ g hV₂ hgP hgN D hd).1

end CFSG.Quasithin.H13
