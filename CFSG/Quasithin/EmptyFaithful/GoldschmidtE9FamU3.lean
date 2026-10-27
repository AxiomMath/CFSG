module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamU3Good
public import CFSG.Quasithin.EmptyFaithful.T1521SU3Main

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Goldschmidt CFSG.Quasithin.U31521
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open CFSG.ProperTwoGeneratedCore.RootCenter

variable {G : Type} [Group G] [Finite G]

theorem nc9U3 {S L : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hL : IsPSU 3 2 n ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ H : Subgroup G, H ≤ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ∧
      H ≤ Subgroup.normalizer (thompsonJ S : Set G) ∧ Odd (Nat.card H) ∧
      ∀ H₀ : Subgroup G, H₀ ≤ H → H₀.relIndex H ∣ 3 →
        (∀ v ∈ S, (∀ x ∈ S ⊓ L, v * x = x * v) → (∀ h ∈ H₀, v * h = h * v) →
          ∀ l ∈ L, v * l = l * v) ∧
        (∀ x ∈ centerOf (S ⊓ L), (∀ h ∈ H₀, x * h = h * x) → x ∈ centerOf L) := by
  classical
  have hn2 : 2 ≤ n := by omega
  obtain ⟨b, hbS, hb2, hcover⟩ := exists_involution_cover hn2 hL hSyl hS2 hSN
  set R : Subgroup G := S ⊓ L with hRdef
  set R' : Sylow 2 ↥L := A4.toSylow hSyl with hR'
  have hR'mem : ∀ x : ↥L, x ∈ (R' : Subgroup ↥L) ↔ (x : G) ∈ R := fun x => Iff.rfl
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hSN hbS
  set β : MulAut ↥L := U31521.conjAut L b hbN with hβ
  have hβstab : β ∈ autStab (R' : Subgroup ↥L) := U31521.conjAut_mem_autStab hSyl hSN hbS
  have hβ2 : β ^ 2 = 1 := by
    ext x
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hβ, U31521.coe_conjAut_apply,
      U31521.coe_conjAut_apply]
    have h1 : b * (b * (x : G) * b⁻¹) * b⁻¹ = (b * b) * (x : G) * (b * b)⁻¹ := by group
    rw [h1, ← pow_two, hb2]
    group
  obtain ⟨r, w, hrR', hwN, hwodd', hfix, hcentr⟩ := exists_goodElt9 hn hL R' hβstab hβ2
  have hrR : (r : G) ∈ R := hrR'
  have hrS : (r : G) ∈ S := hrR.1
  set b' : G := (r : G)⁻¹ * b with hb'
  have hb'S : b' ∈ S := S.mul_mem (S.inv_mem hrS) hbS
  have hfixG : b' * (w : G) * b'⁻¹ = w := by
    have := congrArg (fun x : ↥L => (x : G)) hfix
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply, hβ,
      U31521.coe_conjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [hb']
    calc (r : G)⁻¹ * b * (w : G) * ((r : G)⁻¹ * b)⁻¹ = (r : G)⁻¹ * (b * (w : G) * b⁻¹) * r := by
          group
      _ = w := this
  have hcomm : b' * (w : G) = (w : G) * b' := by
    calc b' * (w : G) = (b' * (w : G) * b'⁻¹) * b' := by group
      _ = (w : G) * b' := by rw [hfixG]
  set T : Subgroup G := innerPart1521 S L with hT
  have hTS : T ≤ S := innerPart1521_le S L
  have hRT : R ≤ T := le_sup_left
  set S₁ : Subgroup G := T ⊔ Subgroup.zpowers b' with hS₁
  have hS₁S : S₁ ≤ S := sup_le hTS (Subgroup.zpowers_le.mpr hb'S)
  have hJS₁ : thompsonJ S ≤ S₁ := by
    refine iSup₂_le fun A hA a ha => ?_
    have haS : a ∈ S := hA.1 ha
    have ha2 : a ^ 2 = 1 := hA.2.1.2 a ha
    rcases hcover a haS ha2 with h | h
    · exact Subgroup.mem_sup_left h
    · have hae : a = (r : G) * b' * (b⁻¹ * a) := by rw [hb']; group
      rw [hae]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hRT hrR))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b'))) (Subgroup.mem_sup_left h)
  have hJeq : thompsonJ S₁ = thompsonJ S := B6.thompsonJ_eq_of_le hJS₁ hS₁S
  have hwL : (w : G) ∈ L := w.2
  have hwR : (w : G) ∈ Subgroup.normalizer (R : Set G) := coe_mem_normalizer_inf hSyl hwN
  have hwT : ∀ x ∈ T, (w : G) * x * (w : G)⁻¹ ∈ T := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (borel_le_normalizer_innerPart S L ⟨hwL, hwR⟩) x).mp hx
  have hwS₁ : (w : G) ∈ Subgroup.normalizer (S₁ : Set G) := by
    apply A4.mem_normalizer_of_conj_mem
    intro x hx
    refine conj_mem_sup_aux hwT (fun y hy => ?_) hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (w : G) b' := hcomm.symm
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b') k
  have hwodd : Odd (orderOf (w : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hwodd'
  refine ⟨Subgroup.zpowers (w : G), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨hwL, hwR⟩
  · rw [Subgroup.zpowers_le]
    have := normalizer_le_normalizer_thompsonJ S₁ hwS₁
    rwa [hJeq] at this
  · rw [Nat.card_zpowers]
    exact hwodd
  · intro H₀ hH₀ hidx
    have hcommH : ∀ a ∈ Subgroup.zpowers (w : G), ∀ c ∈ Subgroup.zpowers (w : G),
        a * c = c * a := by
      intro a ha c hc
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact ((Commute.refl (w : G)).zpow_zpow i j).eq
    have hw3 : (w : G) ^ 3 ∈ H₀ :=
      pow_three_mem_of_relIndex_dvd_three hcommH hidx _ (Subgroup.mem_zpowers _)
    refine ⟨?_, ?_⟩
    · intro v hvS hvR hvH l hl
      have hvN : v ∈ Subgroup.normalizer (L : Set G) := hSN hvS
      set α : MulAut ↥L := U31521.conjAut L v hvN with hα
      have hαstab : α ∈ autStab (R' : Subgroup ↥L) := U31521.conjAut_mem_autStab hSyl hSN hvS
      have hαfix : ∀ x ∈ (R' : Subgroup ↥L), α x = x := by
        intro x hx
        apply Subtype.ext
        rw [hα, U31521.coe_conjAut_apply]
        have := hvR _ ((hR'mem x).1 hx)
        calc v * (x : G) * v⁻¹ = (x : G) * v * v⁻¹ := by rw [this]
          _ = x := by group
      have hRC := rootCenterData_of_isPSU hn2 hL R'
      have hUR : omegaU (R' : Subgroup ↥L) ≤ (R' : Subgroup ↥L) := fun x hx =>
        ((hRC.center_iff x).1 hx).1
      have hαA : α ∈ rootCenterAut (R' : Subgroup ↥L) (omegaU (R' : Subgroup ↥L)) :=
        ⟨map_eq_iff_aux.mpr (mem_autStab.mp hαstab), fun u hu => hαfix u (hUR hu)⟩
      obtain ⟨z, hz, hαz⟩ := hRC.fix_eq α hαA hαfix
      have hzZ : z ∈ sylowCenter (R' : Subgroup ↥L) :=
        mem_sylowCenter.mpr ⟨hUR hz, fun y hy => (((hRC.center_iff z).1 hz).2 y hy).symm⟩
      have hαw : α (w ^ 3) = w ^ 3 := by
        apply Subtype.ext
        rw [hα, U31521.coe_conjAut_apply]
        have := hvH ((w : G) ^ 3) hw3
        calc v * ((w ^ 3 : ↥L) : G) * v⁻¹ = (w : G) ^ 3 * v * v⁻¹ := by
              rw [Subgroup.coe_pow, this]
          _ = ((w ^ 3 : ↥L) : G) := by rw [Subgroup.coe_pow]; group
      have hzw : w ^ 3 * z = z * w ^ 3 := by
        rw [hαz, MulAut.conj_apply] at hαw
        exact (mul_inv_eq_iff_eq_mul.mp hαw).symm
      have hz1 : z = 1 := hcentr z hzZ hzw
      have hα1 : α = 1 := by rw [hαz, hz1, map_one]
      have := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : G)) hα1
      simp only [hα, U31521.coe_conjAut_apply, MulAut.one_apply] at this
      calc v * l = (v * l * v⁻¹) * v := by group
        _ = l * v := by rw [this]
    · intro x hx hxc
      have hxR : x ∈ R := hx.1
      have hxZ : (⟨x, hxR.2⟩ : ↥L) ∈ sylowCenter (R' : Subgroup ↥L) :=
        mem_sylowCenter.mpr ⟨(hR'mem _).2 hxR, fun y hy =>
          Subtype.ext ((Subgroup.mem_centralizer_iff.1 hx.2 y ((hR'mem y).1 hy)))⟩
      have hxw : w ^ 3 * (⟨x, hxR.2⟩ : ↥L) = (⟨x, hxR.2⟩ : ↥L) * w ^ 3 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow]
        exact (hxc _ hw3).symm
      have hx1 : (⟨x, hxR.2⟩ : ↥L) = 1 := hcentr _ hxZ hxw
      have : x = 1 := congrArg Subtype.val hx1
      rw [this]
      exact (centerOf L).one_mem

theorem nrmE9_U3_big (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {X S L : Subgroup G} (hStd : Std1521 X S L) (hc : IsComponentOf L X)
    (_hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) {n : ℕ} (hn : 3 ≤ n) (hty : IsPSU 3 2 n ↥L) :
    NrmE9 S L := by
  have hn2 : 2 ≤ n := by omega
  have horb := a3Orbits_of_a37_a38 (G := G) h37 h38 X S L hStd.sqtk hStd.sylow hStd.comp
  have hS2 : IsPGroup 2 ↥S := hStd.sylow.2.1
  rcases horb.2 with hnorm | ⟨t, htS, htN, hpair, -, -, -⟩
  · obtain ⟨H, h1, h2, h3, h4⟩ := nc9U3 hn hty hStd.sylowL hS2 hnorm
    exact ⟨H, h1.trans le_conjJoin, h2, h3, fun H₀ hH₀ hidx =>
      ⟨fun v hvS _ hvc hvh l hl => (h4 H₀ hH₀ hidx).1 v hvS hvc hvh l hl,
        (h4 H₀ hH₀ hidx).2⟩⟩
  · set S₀ : Subgroup G := S ⊓ Subgroup.normalizer (L : Set G) with hS₀
    have hS₀L : S₀ ⊓ L = S ⊓ L := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, Subgroup.le_normalizer hx.2⟩, hx.2⟩⟩
    have hSyl₀ : IsSylowTwoOf (S₀ ⊓ L) L := by
      rw [hS₀L]
      exact hStd.sylowL
    have hS₀2 : IsPGroup 2 ↥S₀ := hS2.to_inf_left
    obtain ⟨Z, hZR, hZea, hZcard, hiff⟩ := exists_center_u3 hn2 hty hStd.sylowL
    have hq : 3 ≤ 2 ^ n := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hcomm : ⁅L, conjByElt t L⁆ = ⊥ :=
      commutator_conjByElt_eq_bot_u3 hc (hStd.sylow.1 htS) htN
    have hJ : thompsonJ S = thompsonJ S₀ :=
      thompsonJ_eq_inf_normalizer_of_wreath_center hq hZR hZea hZcard
        (fun z hz hc => eq_one_of_central_u3 hn2 hty hz (fun y hy => (hc y hy).symm))
        (fun g hgL hgR hg2 z hz => centralizes_center_of_sq_mem_centralizer hn2 hty hStd.sylowL
          hgL hgR hg2 ((hiff z).1 hz).1 ((hiff z).1 hz).2) hpair hcomm
    obtain ⟨H, h1, h2, h3, h4⟩ := nc9U3 hn hty hSyl₀ hS₀2 inf_le_right
    rw [hS₀L] at h1 h4
    exact ⟨H, h1.trans le_conjJoin, by rw [hJ]; exact h2, h3, fun H₀ hH₀ hidx =>
      ⟨fun v hvS hvN hvc hvh l hl => (h4 H₀ hH₀ hidx).1 v ⟨hvS, hvN⟩ hvc hvh l hl,
        (h4 H₀ hH₀ hidx).2⟩⟩

end CFSG.Quasithin.E9
